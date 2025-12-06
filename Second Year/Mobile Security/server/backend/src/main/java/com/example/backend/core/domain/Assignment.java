package com.example.backend.core.domain;

import java.util.Date;

import jakarta.persistence.Entity;
import jakarta.persistence.Table;

@Entity
@Table(name = "assignment")
public class Assignment {
    private Long id;
    private String title;
    private String description;
    private Long courseId;
    private Long teacherId;
    private Date dueDate;

    public Assignment(String title, String description, Long courseId, Long teacherId, Date dueDate) {
        this.title = title;
        this.description = description;
        this.courseId = courseId;
        this.teacherId = teacherId;
        this.dueDate = dueDate;
    }

    public Long getId() {
        return id;
    }

    public void setId(Long id) {
        this.id = id;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public Long getCourseId() {
        return courseId;
    }

    public void setCourseId(Long courseId) {
        this.courseId = courseId;
    }

    public Date getDueDate() {
        return dueDate;
    }

    public void setDueDate(Date dueDate) {
        this.dueDate = dueDate;
    }

    public Long getTeacherId() {
        return teacherId;
    }

}
