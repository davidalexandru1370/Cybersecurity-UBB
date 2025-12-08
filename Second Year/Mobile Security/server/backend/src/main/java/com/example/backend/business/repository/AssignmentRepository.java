package com.example.backend.business.repository;

import java.util.List;

import org.springframework.data.jpa.repository.JpaRepository;

import com.example.backend.core.domain.Assignment;

public interface AssignmentRepository extends JpaRepository<Assignment, Long> {
    public List<Assignment> findByTeacher_Id(Long teacherId);
}
